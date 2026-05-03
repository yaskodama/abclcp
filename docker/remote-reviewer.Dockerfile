FROM python:3.12-slim
WORKDIR /app
COPY scripts/remote_reviewer_server.py /app/remote_reviewer_server.py
ENV REMOTE_REVIEWER_HOST=0.0.0.0
ENV REMOTE_REVIEWER_PORT=18080
EXPOSE 18080
CMD ["python3", "/app/remote_reviewer_server.py"]
